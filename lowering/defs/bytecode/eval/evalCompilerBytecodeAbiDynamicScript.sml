(* Exact staged Python-oracle bytecode check for dynamic ABI encode/decode. *)

Theory evalCompilerBytecodeAbiDynamic
Ancestors evalCompilerSubsetAbiBuiltins compileVyper concretizeMemLocDefs codegenReadyCompute stackPlanGenCompute alist byte integer_word option cv_std
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

Definition abi_dynamic_n2w_def[nocompute]:
  abi_dynamic_n2w n : bytes32 = n2w n
End

Theorem word_of_bytes_be_bytes32_abi_dynamic:
  (word_of_bytes_be bs : bytes32) =
    abi_dynamic_n2w
      (num_of_bytes (be_bytes (dimindex (:256) DIV 8) [] bs))
Proof
  PURE_REWRITE_TAC[abi_dynamic_n2w_def] >>
  irule word_of_bytes_be_eq_num_of_bytes >> EVAL_TAC
QED

Theorem w2n_abi_dynamic_n2w[compute]:
  w2n (abi_dynamic_n2w n) = n MOD dimword (:256)
Proof
  simp[abi_dynamic_n2w_def]
QED

Theorem get_byte_set_byte_bytes32_abi_dynamic:
  get_byte a (set_byte a b (w : bytes32) be) be = b
Proof
  simp[byteTheory.get_byte_set_byte]
QED

Theorem get_byte_set_byte_irrelevant_bytes32_abi_dynamic:
  w2n (a : bytes32) MOD 32 <> w2n a' MOD 32 ==>
  get_byte a' (set_byte a b (w : bytes32) be) be = get_byte a' w be
Proof
  simp[byteTheory.get_byte_set_byte_irrelevant]
QED

Theorem word_to_bytes_be_bytes32_genlist_abi_dynamic:
  word_to_bytes_be (w : bytes32) =
    GENLIST (λi. get_byte (n2w i) w T) 32
Proof
  simp[listTheory.LIST_EQ_REWRITE, byteTheory.word_to_bytes_be_def,
       byteTheory.word_to_bytes_def, byteTheory.EL_word_to_bytes_aux]
QED

Theorem word_of_bytes_be_word_to_bytes_be_abi_dynamic:
  word_of_bytes_be (word_to_bytes_be (w : bytes32)) = w
Proof
  simp[byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes]
QED

val () = computeLib.upd_compset (computeLib.add_thms
  [word_of_bytes_be_bytes32_abi_dynamic, w2n_abi_dynamic_n2w])

val abi_dynamic_policy_eval = save_thm
  ("abi_dynamic_policy_eval",
   EVAL ``resolve_o1_policy (o1_policy all_capabilities)``)
val abi_dynamic_rpolicy = optionSyntax.dest_some
  (rhs (concl abi_dynamic_policy_eval))
val abi_dynamic_lower_runtime_eval = save_thm
  ("abi_dynamic_lower_runtime_eval",
   EVAL ``lower_vyper_runtime_unit task090_abi_dynamic_program
       ^abi_dynamic_rpolicy``)
val abi_dynamic_runtime_unit = optionSyntax.dest_some
  (rhs (concl abi_dynamic_lower_runtime_eval))
Theorem abi_dynamic_lower_runtime_computed: T
Proof
  simp[]
QED
val abi_dynamic_pre_walk_eval = save_thm
  ("abi_dynamic_pre_walk_eval",
   EVAL ``run_pipeline_stages ^abi_dynamic_rpolicy
       o1_pipeline_spec.ps_pre_walk_stages ^abi_dynamic_runtime_unit
       (init_ir_supply ^abi_dynamic_runtime_unit)``)
Theorem abi_dynamic_pre_walk_computed: T
Proof
  simp[]
QED
val abi_dynamic_pre_pair = optionSyntax.dest_some
  (rhs (concl abi_dynamic_pre_walk_eval))
val abi_dynamic_pre_unit = #1 (pairSyntax.dest_pair abi_dynamic_pre_pair)
val abi_dynamic_pre_supply = #2 (pairSyntax.dest_pair abi_dynamic_pre_pair)
val abi_dynamic_fcg_eval = EVAL
  ``fcg_analyze (^abi_dynamic_pre_unit).cu_context``
val abi_dynamic_walk_unit_eval = EVAL
  ``prune_unit_fcg_unreachable ^abi_dynamic_pre_unit
      ^(rhs (concl abi_dynamic_fcg_eval))``
val abi_dynamic_walk_unit = rhs (concl abi_dynamic_walk_unit_eval)
val abi_dynamic_entry_eval = EVAL
  ``(^abi_dynamic_pre_unit).cu_context.ctx_entry``
val abi_dynamic_entry = optionSyntax.dest_some
  (rhs (concl abi_dynamic_entry_eval))
val abi_dynamic_order_eval = EVAL
  ``fcg_postorder ^(rhs (concl abi_dynamic_fcg_eval)) ^abi_dynamic_entry``
val abi_dynamic_walk_eval = save_thm
  ("abi_dynamic_walk_eval",
   EVAL ``run_callee_first ^abi_dynamic_rpolicy o1_fn_passes
       ^(rhs (concl abi_dynamic_order_eval)) ^abi_dynamic_walk_unit
       ^abi_dynamic_pre_supply``)
Theorem abi_dynamic_walk_computed: T
Proof
  simp[]
QED
val abi_dynamic_walk_pair = optionSyntax.dest_some
  (rhs (concl abi_dynamic_walk_eval))
val abi_dynamic_walked_unit = #1 (pairSyntax.dest_pair abi_dynamic_walk_pair)
val abi_dynamic_walked_supply = #2 (pairSyntax.dest_pair abi_dynamic_walk_pair)
val abi_dynamic_post_walk_eval = save_thm
  ("abi_dynamic_post_walk_eval",
   EVAL ``run_pipeline_stages ^abi_dynamic_rpolicy
       o1_pipeline_spec.ps_post_walk_stages ^abi_dynamic_walked_unit
       ^abi_dynamic_walked_supply``)
Theorem abi_dynamic_post_walk_computed: T
Proof
  simp[]
QED
val abi_dynamic_post_pair = optionSyntax.dest_some
  (rhs (concl abi_dynamic_post_walk_eval))
val abi_dynamic_final_checked_unit = #1 (pairSyntax.dest_pair abi_dynamic_post_pair)
val abi_dynamic_final_supply = #2 (pairSyntax.dest_pair abi_dynamic_post_pair)
val abi_dynamic_initial_checks_eval = EVAL
  ``pipeline_spec_wf ^abi_dynamic_rpolicy o1_pipeline_spec /\
    unit_wf ^abi_dynamic_runtime_unit /\
    raw_static_inputs_wf (^abi_dynamic_runtime_unit).cu_context``
val abi_dynamic_pre_acyclic_eval = EVAL
  ``reachable_fcg_acyclic (^abi_dynamic_pre_unit).cu_context
      ^(rhs (concl abi_dynamic_fcg_eval))``
val abi_dynamic_final_unit_wf = save_thm
  ("abi_dynamic_final_unit_wf", EQT_ELIM
    (EVAL ``unit_wf ^abi_dynamic_final_checked_unit``))
val abi_dynamic_final_labels_wf = save_thm
  ("abi_dynamic_final_labels_wf", EQT_ELIM
    (EVAL ``unit_labels_wf ^abi_dynamic_final_checked_unit``))
val abi_dynamic_final_target_safe = save_thm
  ("abi_dynamic_final_target_safe", EQT_ELIM
    (EVAL ``context_target_safe (^abi_dynamic_rpolicy).rpol_target
      (^abi_dynamic_final_checked_unit).cu_context``))
val abi_dynamic_final_layout_wf = save_thm
  ("abi_dynamic_final_layout_wf", EQT_ELIM
    (EVAL ``concretized_static_layouts_wf
      (^abi_dynamic_final_checked_unit).cu_context``))
val abi_dynamic_final_fmp_wf = save_thm
  ("abi_dynamic_final_fmp_wf", EQT_ELIM
    (EVAL ``fmp_lowered_context_wf
      (^abi_dynamic_final_checked_unit).cu_context``))
val abi_dynamic_final_acyclic = save_thm
  ("abi_dynamic_final_acyclic", EQT_ELIM
    (EVAL ``reachable_fcg_acyclic
      (^abi_dynamic_final_checked_unit).cu_context
      (fcg_analyze (^abi_dynamic_final_checked_unit).cu_context)``))
val abi_dynamic_ready_fn_eval = save_thm
  ("abi_dynamic_ready_fn_eval",
   EVAL ``HD (^abi_dynamic_final_checked_unit).cu_context.ctx_functions``)
val abi_dynamic_ready_fn = rhs (concl abi_dynamic_ready_fn_eval)
val abi_dynamic_ready_canonical_eval = EVAL
  ``canonical_param_prefix ^abi_dynamic_ready_fn``
val abi_dynamic_ready_wf_fn_eval = EVAL
  ``wf_function ^abi_dynamic_ready_fn``
val abi_dynamic_ready_inst_wf_eval = EVAL
  ``fn_inst_wf ^abi_dynamic_ready_fn``
val abi_dynamic_ready_ssa_eval = EVAL
  ``ssa_form ^abi_dynamic_ready_fn``
val abi_dynamic_ready_cfg_eval = save_thm
  ("abi_dynamic_ready_cfg_eval", EVAL ``cfg_analyze ^abi_dynamic_ready_fn``)
val abi_dynamic_ready_dom_analysis_eval = save_thm
  ("abi_dynamic_ready_dom_analysis_eval",
   EVAL ``dom_analyze ^(rhs (concl abi_dynamic_ready_cfg_eval))
      ^abi_dynamic_ready_fn``)
val abi_dynamic_ready_dom_exec_step1 = SIMP_CONV pure_ss
  [codegenReadyComputeTheory.def_dominates_uses_exec_def,
   abi_dynamic_ready_cfg_eval, abi_dynamic_ready_dom_analysis_eval, LET_THM]
  ``def_dominates_uses_exec ^abi_dynamic_ready_fn``
val () = computeLib.upd_compset
  (fn cs => computeLib.scrub_const cs ``def_available_at_exec``)
val abi_dynamic_ready_dom_exec_step2 = save_thm
  ("abi_dynamic_ready_dom_exec_step2",
   EVAL (rhs (concl abi_dynamic_ready_dom_exec_step1)))
val abi_dynamic_ready_available_terms = find_terms
  (can (match_term ``def_available_at_exec cfg dom fn bb use_opt v``))
  (rhs (concl abi_dynamic_ready_dom_exec_step2))
val () =
  if length abi_dynamic_ready_available_terms = 495 then ()
  else raise Fail "expected 495 ABI-dynamic availability calls"
val () = computeLib.upd_compset (computeLib.add_thms
  [codegenReadyComputeTheory.def_available_at_exec_def])
fun abi_dynamic_take_chunk _ [] = ([],[])
  | abi_dynamic_take_chunk 0 xs = ([],xs)
  | abi_dynamic_take_chunk n (x::xs) = let
      val (front,rest) = abi_dynamic_take_chunk (n - 1) xs
    in (x::front,rest) end
fun abi_dynamic_rewrite_available current [] = current
  | abi_dynamic_rewrite_available current terms = let
      val (chunk,rest) = abi_dynamic_take_chunk 40 terms
      val evals = map EVAL chunk
      val step = PURE_REWRITE_CONV evals (rhs (concl current))
    in
      abi_dynamic_rewrite_available (TRANS current step) rest
    end
val abi_dynamic_ready_dom_exec_step3 =
  abi_dynamic_rewrite_available
    (REFL (rhs (concl abi_dynamic_ready_dom_exec_step2)))
    abi_dynamic_ready_available_terms
val abi_dynamic_ready_dom_exec_eval =
  TRANS abi_dynamic_ready_dom_exec_step1
    (TRANS abi_dynamic_ready_dom_exec_step2
      (TRANS abi_dynamic_ready_dom_exec_step3
        (EVAL (rhs (concl abi_dynamic_ready_dom_exec_step3)))))
val abi_dynamic_ready_dom_eval = prove
  (``def_dominates_uses ^abi_dynamic_ready_fn``,
   simp[codegenReadyComputeTheory.def_dominates_uses_compute,
        abi_dynamic_ready_wf_fn_eval, abi_dynamic_ready_dom_exec_eval])
val abi_dynamic_ready_sue_eval = EVAL
  ``single_use_form ^abi_dynamic_ready_fn``
val abi_dynamic_ready_cfg_norm_eval = EVAL
  ``cfg_is_normalized (cfg_analyze ^abi_dynamic_ready_fn)
      ^abi_dynamic_ready_fn``
val () = computeLib.upd_compset (computeLib.add_thms
  [stackPlanGenTheory.codegen_ready_inst_def,
   stackPlanGenTheory.is_pre_codegen_opcode_def,
   stackPlanGenTheory.is_unlowered_fmp_opcode_def,
   stackPlanGenTheory.is_unlowered_internal_call_opcode_def,
   stackPlanGenTheory.invoke_operands_wf_def])
val abi_dynamic_ready_insts_step1 = TRY_CONV EVAL
  ``EVERY (λbb. EVERY codegen_ready_inst bb.bb_instructions)
      (^abi_dynamic_ready_fn).fn_blocks``
val abi_dynamic_ready_insts_eval = TRANS abi_dynamic_ready_insts_step1
  (TRY_CONV EVAL (rhs (concl abi_dynamic_ready_insts_step1)))
val abi_dynamic_ready_fn_rhs = LIST_CONJ
  [EQT_ELIM abi_dynamic_ready_canonical_eval,
   EQT_ELIM abi_dynamic_ready_wf_fn_eval,
   EQT_ELIM abi_dynamic_ready_inst_wf_eval,
   EQT_ELIM abi_dynamic_ready_ssa_eval,
   abi_dynamic_ready_dom_eval,
   EQT_ELIM abi_dynamic_ready_sue_eval,
   EQT_ELIM abi_dynamic_ready_cfg_norm_eval,
   EQT_ELIM abi_dynamic_ready_insts_eval]
val abi_dynamic_ready_fn_thm = prove
  (``codegen_ready_fn ^abi_dynamic_ready_fn``,
   PURE_REWRITE_TAC [stackPlanGenTheory.codegen_ready_fn_def] >>
   ACCEPT_TAC abi_dynamic_ready_fn_rhs)
val abi_dynamic_codegen_shell = SIMP_CONV (srw_ss())
  [stackPlanGenTheory.codegen_ready_def, abi_dynamic_ready_fn_eval]
  ``codegen_ready (^abi_dynamic_final_checked_unit).cu_context``
val abi_dynamic_actual_ready_calls = find_terms
  (can (match_term ``codegen_ready_fn fn``))
  (rhs (concl abi_dynamic_codegen_shell))
val abi_dynamic_actual_ready_call = hd abi_dynamic_actual_ready_calls
val abi_dynamic_actual_ready_fn = #2 (dest_comb abi_dynamic_actual_ready_call)
Theorem abi_dynamic_i2w_neg_num:
  ∀n. i2w (-&n) = -n2w n
Proof
  Cases_on `n` >> simp[i2w_def]
QED
val () = computeLib.upd_compset
  (computeLib.add_thms [abi_dynamic_i2w_neg_num])
fun abi_dynamic_ready_w2n_eval w =
  if same_const (#1 (strip_comb w)) ``set_byte`` then let
    val bytes_th = SIMP_CONV (srw_ss())
      [word_to_bytes_be_bytes32_genlist_abi_dynamic,
       get_byte_set_byte_bytes32_abi_dynamic,
       get_byte_set_byte_irrelevant_bytes32_abi_dynamic]
      ``word_to_bytes_be ^w``
    val roundtrip = INST [``w:bytes32`` |-> w]
      word_of_bytes_be_word_to_bytes_be_abi_dynamic
    val step1 = BETA_RULE (AP_TERM ``λx:bytes32. w2n x`` (SYM roundtrip))
    val step2 = BETA_RULE (AP_TERM
      ``λbs. w2n (word_of_bytes_be bs : bytes32)`` bytes_th)
    val decoded = TRANS step1 step2
    val expose = SIMP_CONV bool_ss
      [word_of_bytes_be_bytes32_abi_dynamic, w2n_abi_dynamic_n2w]
      (rhs (concl decoded))
  in
    TRANS decoded (TRANS expose (EVAL (rhs (concl expose))))
  end else EVAL ``w2n ^w``

fun abi_dynamic_ready_normalize_word w = let
  val w2n_th = abi_dynamic_ready_w2n_eval w
  val numeral = rhs (concl w2n_th)
  val normalized = ``n2w ^numeral : bytes32``
  val normalized_w2n = EVAL ``w2n ^normalized``
  val same_num = TRANS w2n_th (SYM normalized_w2n)
in
  EQ_MP (ISPECL [w,normalized] wordsTheory.w2n_11) same_num
end
val abi_dynamic_ready_words = List.foldl
  (fn (lit,ws) => let val w = #2 (dest_comb lit) in
      if List.exists (aconv w) ws then ws else w::ws end) []
  (find_terms (can (match_term ``Lit w``))
    (mk_eq (abi_dynamic_actual_ready_fn,abi_dynamic_ready_fn)))
val abi_dynamic_ready_word_normalizations =
  map abi_dynamic_ready_normalize_word abi_dynamic_ready_words
val abi_dynamic_ready_fn_eq_step = SIMP_CONV (srw_ss())
  (abi_dynamic_n2w_def :: abi_dynamic_ready_word_normalizations)
  (mk_eq (abi_dynamic_actual_ready_fn,abi_dynamic_ready_fn))
val abi_dynamic_ready_fn_eq_tail =
  EVAL (rhs (concl abi_dynamic_ready_fn_eq_step))
val abi_dynamic_ready_fn_eq = EQT_ELIM
  (TRANS abi_dynamic_ready_fn_eq_step abi_dynamic_ready_fn_eq_tail)
val abi_dynamic_actual_ready_fn_thm = EQ_MP
  (SYM (AP_TERM ``codegen_ready_fn`` abi_dynamic_ready_fn_eq))
  abi_dynamic_ready_fn_thm
val abi_dynamic_final_codegen_ready = save_thm
  ("abi_dynamic_final_codegen_ready",
   EQ_MP (SYM abi_dynamic_codegen_shell) abi_dynamic_actual_ready_fn_thm)
val abi_dynamic_final_checks_eval = save_thm
  ("abi_dynamic_final_checks_eval", EQT_INTRO (LIST_CONJ
    [abi_dynamic_final_unit_wf, abi_dynamic_final_labels_wf,
     abi_dynamic_final_target_safe, abi_dynamic_final_layout_wf,
     abi_dynamic_final_fmp_wf, abi_dynamic_final_acyclic,
     abi_dynamic_final_codegen_ready]))
Theorem abi_dynamic_final_checks_computed: T
Proof
  simp[]
QED
val abi_dynamic_spec_pre_eval = EVAL
  ``o1_pipeline_spec.ps_pre_walk_stages``
val abi_dynamic_spec_prune_eval = EVAL
  ``o1_pipeline_spec.ps_prune_unreachable``
val abi_dynamic_spec_acyclic_eval = EVAL
  ``o1_pipeline_spec.ps_require_acyclic_calls``
val abi_dynamic_spec_passes_eval = SIMP_CONV (srw_ss())
  [venomPassScheduleTheory.o1_pipeline_spec_def]
  ``o1_pipeline_spec.ps_fn_passes``
val abi_dynamic_spec_post_eval = EVAL
  ``o1_pipeline_spec.ps_post_walk_stages``
val abi_dynamic_spec_final_asm_eval = EVAL
  ``o1_pipeline_spec.ps_final_assembly``
val abi_dynamic_initial_check_rules = map EQT_INTRO
  (CONJUNCTS (EQT_ELIM abi_dynamic_initial_checks_eval))
val abi_dynamic_final_check_rules = map EQT_INTRO
  (CONJUNCTS (EQT_ELIM abi_dynamic_final_checks_eval))
val abi_dynamic_pipeline_rules =
  abi_dynamic_initial_check_rules @
  [abi_dynamic_pre_walk_eval, abi_dynamic_spec_pre_eval,
   abi_dynamic_fcg_eval, abi_dynamic_spec_prune_eval,
   abi_dynamic_walk_unit_eval, abi_dynamic_spec_acyclic_eval,
   abi_dynamic_pre_acyclic_eval, abi_dynamic_entry_eval,
   abi_dynamic_spec_passes_eval, abi_dynamic_order_eval,
   abi_dynamic_walk_eval, abi_dynamic_post_walk_eval,
   abi_dynamic_spec_post_eval] @ abi_dynamic_final_check_rules @
  [abi_dynamic_spec_final_asm_eval]
val abi_dynamic_admin_rules =
  [LET_THM, COND_CLAUSES, NOT_CLAUSES, boolTheory.AND_CLAUSES,
   combinTheory.K_THM, optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF,
   optionTheory.THE_DEF, pairTheory.pair_case_thm]
val abi_dynamic_admin_rewrites = List.concat
  (map (CONJUNCTS o SPEC_ALL) abi_dynamic_admin_rules)
val abi_dynamic_admin_conv = FIRST_CONV
  (BETA_CONV :: map REWR_CONV abi_dynamic_admin_rewrites)
fun abi_dynamic_repeat_admin 0 tm = REFL tm
  | abi_dynamic_repeat_admin n tm =
      (case total (ONCE_DEPTH_CONV abi_dynamic_admin_conv) tm of
         NONE => REFL tm
       | SOME th => TRANS th
           (abi_dynamic_repeat_admin (n - 1) (rhs (concl th))))
fun abi_dynamic_apply_stage stage_th current =
  case total (ONCE_DEPTH_CONV (REWR_CONV stage_th)) (rhs (concl current)) of
    NONE => current
  | SOME staged => let
      val admin = abi_dynamic_repeat_admin 30 (rhs (concl staged))
    in TRANS current (TRANS staged admin) end
fun abi_dynamic_apply_stages current [] = current
  | abi_dynamic_apply_stages current (th::ths) =
      abi_dynamic_apply_stages (abi_dynamic_apply_stage th current) ths
val abi_dynamic_run_pipeline_initial0 = SIMP_CONV pure_ss
  [venomPipelineDriverTheory.run_venom_pipeline_def]
  ``run_venom_pipeline (K T) (K T) (K T)
       ^abi_dynamic_rpolicy o1_pipeline_spec ^abi_dynamic_runtime_unit``
val abi_dynamic_run_pipeline_initial = TRANS abi_dynamic_run_pipeline_initial0
  (abi_dynamic_repeat_admin 30
    (rhs (concl abi_dynamic_run_pipeline_initial0)))
val abi_dynamic_run_pipeline_eval = save_thm
  ("abi_dynamic_run_pipeline_eval",
   abi_dynamic_apply_stages abi_dynamic_run_pipeline_initial
     abi_dynamic_pipeline_rules)
Theorem abi_dynamic_pipeline_computed: T
Proof
  simp[]
QED
val abi_dynamic_pipeline_out = optionSyntax.dest_some
  (rhs (concl abi_dynamic_run_pipeline_eval))
val abi_dynamic_final_unit = rhs (concl (EVAL
  ``(^abi_dynamic_pipeline_out).po_unit``))

val abi_dynamic_max_eom_eval = save_thm
  ("abi_dynamic_max_eom_eval", EVAL
    ``max_live_eom (^abi_dynamic_final_unit).cu_context``)
val abi_dynamic_max_eom = optionSyntax.dest_some
  (rhs (concl abi_dynamic_max_eom_eval))
val abi_dynamic_final_fn_eval = EVAL
  ``HD (^abi_dynamic_final_unit).cu_context.ctx_functions``
val abi_dynamic_final_fn = rhs (concl abi_dynamic_final_fn_eval)
fun abi_dynamic_w2n_eval w = let
  val bytes_th = SIMP_CONV (srw_ss())
    [word_to_bytes_be_bytes32_genlist_abi_dynamic,
     get_byte_set_byte_bytes32_abi_dynamic,
     get_byte_set_byte_irrelevant_bytes32_abi_dynamic]
    ``word_to_bytes_be ^w``
  val roundtrip = INST [``w:bytes32`` |-> w]
    word_of_bytes_be_word_to_bytes_be_abi_dynamic
  val step1 = BETA_RULE (AP_TERM ``λx:bytes32. w2n x`` (SYM roundtrip))
  val step2 = BETA_RULE (AP_TERM
    ``λbs. w2n (word_of_bytes_be bs : bytes32)`` bytes_th)
  val decoded = TRANS step1 step2
  val expose = SIMP_CONV bool_ss
    [word_of_bytes_be_bytes32_abi_dynamic, w2n_abi_dynamic_n2w]
    (rhs (concl decoded))
in
  TRANS decoded (TRANS expose (EVAL (rhs (concl expose))))
end
fun abi_dynamic_normalize_word w = let
  val w2n_th = abi_dynamic_w2n_eval w
  val numeral = rhs (concl w2n_th)
  val normalized = ``n2w ^numeral : bytes32``
  val normalized_w2n = EVAL ``w2n ^normalized``
  val same_num = TRANS w2n_th (SYM normalized_w2n)
in
  EQ_MP (ISPECL [w,normalized] wordsTheory.w2n_11) same_num
end
val abi_dynamic_set_byte_words = List.foldl
  (fn (tm,ws) => if List.exists (aconv tm) ws then ws else tm::ws) []
  (find_terms (can (match_term ``set_byte a b w be : bytes32``))
    abi_dynamic_final_fn)
val abi_dynamic_word_normalizations =
  map abi_dynamic_normalize_word abi_dynamic_set_byte_words
val abi_dynamic_final_fn_normalized_eval =
  if null abi_dynamic_word_normalizations then REFL abi_dynamic_final_fn
  else PURE_REWRITE_CONV abi_dynamic_word_normalizations abi_dynamic_final_fn
val abi_dynamic_final_fn_normalized =
  rhs (concl abi_dynamic_final_fn_normalized_eval)
val abi_dynamic_plan_canonical_eval = EVAL
  ``canonical_param_prefix ^abi_dynamic_final_fn_normalized``
val abi_dynamic_plan_live_eval = save_thm
  ("abi_dynamic_plan_live_eval",
   EVAL ``liveness_analyze ^abi_dynamic_final_fn_normalized``)
val abi_dynamic_plan_dfg_eval = EVAL
  ``dfg_build_function ^abi_dynamic_final_fn_normalized``
val abi_dynamic_plan_cfg_eval = EVAL
  ``cfg_analyze ^abi_dynamic_final_fn_normalized``
val abi_dynamic_plan_entry_eval = EVAL
  ``fn_entry_label ^abi_dynamic_final_fn_normalized``
val abi_dynamic_plan_entry = optionSyntax.dest_some
  (rhs (concl abi_dynamic_plan_entry_eval))
val abi_dynamic_plan_initial_state_eval = EVAL
  ``(init_plan_state ^abi_dynamic_max_eom) with ps_label_counter := 0``
val abi_dynamic_plan_initial_state =
  rhs (concl abi_dynamic_plan_initial_state_eval)
val abi_dynamic_plan_aux_fuel_step1 = save_thm
  ("abi_dynamic_plan_aux_fuel_step1",
   EVAL ``generate_fn_plan_aux_fuel 30
      ^(rhs (concl abi_dynamic_plan_live_eval))
      ^(rhs (concl abi_dynamic_plan_dfg_eval))
      ^(rhs (concl abi_dynamic_plan_cfg_eval)) ^abi_dynamic_final_fn_normalized
      [^abi_dynamic_plan_entry] [] ^abi_dynamic_plan_initial_state``)
Theorem abi_dynamic_plan_aux_fuel_step1_computed: T
Proof
  simp[]
QED
val abi_dynamic_plan_aux_fuel_eval = abi_dynamic_plan_aux_fuel_step1
val abi_dynamic_plan_aux_result = optionSyntax.dest_some
  (rhs (concl abi_dynamic_plan_aux_fuel_eval))
val abi_dynamic_plan_aux_sound = CONJUNCT1
  (SPEC ``30`` generate_plan_fuel_some)
val abi_dynamic_plan_aux_eval = MATCH_MP
  (SPEC_ALL abi_dynamic_plan_aux_sound)
  abi_dynamic_plan_aux_fuel_eval
val abi_dynamic_plan_analyzed_eval = save_thm
  ("abi_dynamic_plan_analyzed_eval",
   SIMP_CONV (srw_ss())
    [stackPlanGenTheory.generate_fn_plan_analyzed_def,
     abi_dynamic_plan_canonical_eval, abi_dynamic_plan_entry_eval,
     abi_dynamic_plan_initial_state_eval, abi_dynamic_plan_aux_eval]
    ``generate_fn_plan_analyzed
        ^(rhs (concl abi_dynamic_plan_live_eval))
        ^(rhs (concl abi_dynamic_plan_dfg_eval))
        ^(rhs (concl abi_dynamic_plan_cfg_eval))
        ^abi_dynamic_final_fn_normalized ^abi_dynamic_max_eom 0``)
val abi_dynamic_fn_plan_step1 = REWR_CONV
  stackPlanGenTheory.generate_fn_plan_def
  ``generate_fn_plan ^abi_dynamic_final_fn_normalized ^abi_dynamic_max_eom 0``
val abi_dynamic_fn_plan_step2 = PURE_REWRITE_CONV
  [abi_dynamic_plan_live_eval, abi_dynamic_plan_dfg_eval,
   abi_dynamic_plan_cfg_eval]
  (rhs (concl abi_dynamic_fn_plan_step1))
val abi_dynamic_fn_plan_step3 = REWR_CONV abi_dynamic_plan_analyzed_eval
  (rhs (concl abi_dynamic_fn_plan_step2))
val abi_dynamic_normalized_fn_plan_eval =
  TRANS abi_dynamic_fn_plan_step1
    (TRANS abi_dynamic_fn_plan_step2 abi_dynamic_fn_plan_step3)
val abi_dynamic_fn_plan_congruence = BETA_RULE (AP_TERM
  ``λfn. generate_fn_plan fn ^abi_dynamic_max_eom 0``
  abi_dynamic_final_fn_normalized_eval)
val abi_dynamic_fn_plan_eval = save_thm
  ("abi_dynamic_fn_plan_eval",
   TRANS abi_dynamic_fn_plan_congruence abi_dynamic_normalized_fn_plan_eval)
Theorem abi_dynamic_fn_plan_computed: T
Proof
  simp[]
QED
val () = computeLib.upd_compset (computeLib.add_thms
  [abi_dynamic_max_eom_eval, abi_dynamic_fn_plan_eval])
val abi_dynamic_context_plan_eval = save_thm
  ("abi_dynamic_context_plan_eval",
   EVAL ``generate_context_plan (^abi_dynamic_final_unit).cu_context``)
val abi_dynamic_context_plan = optionSyntax.dest_some
  (rhs (concl abi_dynamic_context_plan_eval))
val abi_dynamic_plan_ops_eval = EVAL
  ``context_plan_ops ^abi_dynamic_context_plan``
val abi_dynamic_initial_fmp_eval = EVAL
  ``(^abi_dynamic_context_plan).cp_initial_fmp``
val abi_dynamic_execute_plan_eval = save_thm
  ("abi_dynamic_execute_plan_eval",
   EVAL ``execute_plan ^(rhs (concl abi_dynamic_initial_fmp_eval))
       ^(rhs (concl abi_dynamic_plan_ops_eval))``)
val abi_dynamic_data_asm_eval = EVAL
  ``data_segment_asm (^abi_dynamic_final_unit).cu_data_segment``
val abi_dynamic_raw_asm_eval = EVAL
  ``^(rhs (concl abi_dynamic_execute_plan_eval)) ++
    ^(rhs (concl abi_dynamic_data_asm_eval)) ++ [AsmDataHeader "code_end"]``
val abi_dynamic_raw_asm = rhs (concl abi_dynamic_raw_asm_eval)
val abi_dynamic_target_wf_eval = EVAL
  ``target_capabilities_wf (^abi_dynamic_rpolicy).rpol_target``
val abi_dynamic_context_safe_eval = EVAL
  ``context_target_safe (^abi_dynamic_rpolicy).rpol_target
      (^abi_dynamic_final_unit).cu_context``
val abi_dynamic_assembly_safe_eval = EVAL
  ``assembly_target_safe (^abi_dynamic_rpolicy).rpol_target
      ^abi_dynamic_raw_asm``
val abi_dynamic_codegen_step0 = SIMP_CONV pure_ss
  [codegenTheory.codegen_assembly_def, abi_dynamic_target_wf_eval,
   abi_dynamic_context_safe_eval, abi_dynamic_context_plan_eval,
   optionTheory.option_case_compute, optionTheory.IS_SOME_DEF,
   optionTheory.THE_DEF, LET_THM, NOT_CLAUSES, COND_CLAUSES]
  ``codegen_assembly ^abi_dynamic_rpolicy ^abi_dynamic_final_unit``
val abi_dynamic_codegen_step1 = SIMP_CONV pure_ss
  [abi_dynamic_plan_ops_eval, abi_dynamic_initial_fmp_eval,
   abi_dynamic_execute_plan_eval, abi_dynamic_data_asm_eval,
   abi_dynamic_raw_asm_eval, abi_dynamic_assembly_safe_eval]
  (rhs (concl abi_dynamic_codegen_step0))
val abi_dynamic_codegen_eval = save_thm
  ("abi_dynamic_codegen_eval",
   TRANS abi_dynamic_codegen_step0
     (TRANS abi_dynamic_codegen_step1
       (EVAL (rhs (concl abi_dynamic_codegen_step1)))))
val abi_dynamic_finalize_step0 =
  REWR_CONV codegenTheory.finalize_codegen_identity
    ``finalize_codegen (K SOME) ^abi_dynamic_rpolicy ^abi_dynamic_final_unit``
val abi_dynamic_finalize_step1 = PURE_REWRITE_CONV
  [abi_dynamic_codegen_eval] (rhs (concl abi_dynamic_finalize_step0))
val abi_dynamic_finalize_eval = save_thm
  ("abi_dynamic_finalize_eval",
   TRANS abi_dynamic_finalize_step0
     (TRANS abi_dynamic_finalize_step1
       (EVAL (rhs (concl abi_dynamic_finalize_step1)))))
val abi_dynamic_runtime_bytes = optionSyntax.dest_some
  (rhs (concl abi_dynamic_finalize_eval))

val abi_dynamic_lower_deploy_eval = save_thm
  ("abi_dynamic_lower_deploy_eval",
   EVAL ``lower_vyper_deploy_unit task090_abi_dynamic_program
       ^abi_dynamic_rpolicy ^abi_dynamic_runtime_bytes``)
val abi_dynamic_deploy_unit = optionSyntax.dest_some
  (rhs (concl abi_dynamic_lower_deploy_eval))
val abi_dynamic_deploy_pipeline_eval = save_thm
  ("abi_dynamic_deploy_pipeline_eval",
   EVAL ``run_venom_pipeline (K T) (K T) (K T)
       ^abi_dynamic_rpolicy o1_pipeline_spec ^abi_dynamic_deploy_unit``)
val abi_dynamic_deploy_out = optionSyntax.dest_some
  (rhs (concl abi_dynamic_deploy_pipeline_eval))
val abi_dynamic_final_deploy_unit = rhs (concl (EVAL
  ``(^abi_dynamic_deploy_out).po_unit``))
val abi_dynamic_finalize_deploy_eval = save_thm
  ("abi_dynamic_finalize_deploy_eval",
   EVAL ``finalize_codegen (K SOME) ^abi_dynamic_rpolicy
       ^abi_dynamic_final_deploy_unit``)

val abi_dynamic_compile_term =
  ``compile_vyper (K SOME) (o1_policy all_capabilities)
      task090_abi_dynamic_program``
val abi_dynamic_compile_step0 = SIMP_CONV pure_ss
  [compileVyperTheory.compile_vyper_def,
   compileVyperTheory.compile_vyper_with_def,
   compileVyperTheory.checked_unit_pipeline_def,
   optionTheory.option_case_def, boolTheory.COND_CLAUSES,
   abi_dynamic_policy_eval, abi_dynamic_lower_runtime_eval,
   abi_dynamic_run_pipeline_eval, abi_dynamic_finalize_eval,
   abi_dynamic_lower_deploy_eval, abi_dynamic_deploy_pipeline_eval,
   abi_dynamic_finalize_deploy_eval, LET_THM, pairTheory.FST,
   pairTheory.SND, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  abi_dynamic_compile_term
val abi_dynamic_compile_eval = TRANS abi_dynamic_compile_step0
  (EVAL (rhs (concl abi_dynamic_compile_step0)))
val abi_dynamic_compile_eval = save_thm
  ("abi_dynamic_compile_eval", abi_dynamic_compile_eval)
Theorem abi_dynamic_compile_computed: T
Proof
  simp[]
QED
val abi_dynamic_oracle_eq = EQT_ELIM (EVAL (mk_eq
  (rhs (concl abi_dynamic_compile_eval),
   ``SOME ^(evalCompilerBytecodeLib.read_hex_bytes "abi_dynamic.hex")``)))
val abi_dynamic_matches_python_oracle = save_thm
  ("abi_dynamic_matches_python_oracle",
   TRANS abi_dynamic_compile_eval abi_dynamic_oracle_eq)

(* The concrete staging theorems are evaluator checkpoints, not API.  Keeping
   only the final parity theorem makes the generated theory load within the
   bounded HOL store. *)
val () = List.app Theory.delete_binding
  ["abi_dynamic_policy_eval",
   "abi_dynamic_lower_runtime_eval", "abi_dynamic_lower_runtime_computed",
   "abi_dynamic_pre_walk_eval", "abi_dynamic_pre_walk_computed",
   "abi_dynamic_walk_eval", "abi_dynamic_walk_computed",
   "abi_dynamic_post_walk_eval", "abi_dynamic_post_walk_computed",
   "abi_dynamic_final_unit_wf", "abi_dynamic_final_labels_wf",
   "abi_dynamic_final_target_safe", "abi_dynamic_final_layout_wf",
   "abi_dynamic_final_fmp_wf", "abi_dynamic_final_acyclic",
   "abi_dynamic_ready_fn_eval", "abi_dynamic_ready_cfg_eval",
   "abi_dynamic_ready_dom_analysis_eval",
   "abi_dynamic_ready_dom_exec_step2", "abi_dynamic_i2w_neg_num",
   "abi_dynamic_final_codegen_ready", "abi_dynamic_final_checks_eval",
   "abi_dynamic_final_checks_computed", "abi_dynamic_run_pipeline_eval",
   "abi_dynamic_pipeline_computed", "abi_dynamic_max_eom_eval",
   "abi_dynamic_plan_live_eval", "abi_dynamic_plan_aux_fuel_step1",
   "abi_dynamic_plan_aux_fuel_step1_computed",
   "abi_dynamic_plan_analyzed_eval", "abi_dynamic_fn_plan_eval",
   "abi_dynamic_fn_plan_computed", "abi_dynamic_context_plan_eval",
   "abi_dynamic_execute_plan_eval", "abi_dynamic_codegen_eval",
   "abi_dynamic_finalize_eval", "abi_dynamic_lower_deploy_eval",
   "abi_dynamic_deploy_pipeline_eval", "abi_dynamic_finalize_deploy_eval",
   "abi_dynamic_compile_eval", "abi_dynamic_compile_computed"]
